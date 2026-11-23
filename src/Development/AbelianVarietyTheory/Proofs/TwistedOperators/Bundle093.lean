module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviRadicalProductLengthOfLatticeSteps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRadicalCosetCountOfHeisenberg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ProdLeadMinorDiagonal
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle088
public import Formalism.LocalRingCardinality.DataTheta
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.leviRadicalProductLength_of_lattice_steps : AddVec → Dual → SpanEq → Heis → Pointwise := by
  first | exact @GlobalTheory.InertZeta.pointwise_of_steps | exact GlobalTheory.InertZeta.pointwise_of_steps | (intros; apply GlobalTheory.InertZeta.pointwise_of_steps <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.smallRadicalCosetCount_of_heisenberg : Heis → LatIndex → TraceIndex → Count := by
  first | exact @GlobalTheory.InertZeta.count_of_heis | exact GlobalTheory.InertZeta.count_of_heis | (intros; apply GlobalTheory.InertZeta.count_of_heis <;> assumption)
end

section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm.ListShape

def posFn (x : List ℤ) (i : ℕ) : ℕ := (x.getD i 0).toNat

def negFn (y : List ℤ) (i : ℕ) : ℕ := posFn (y.reverse.map fun v => -v) i

theorem posFn_eq_zero {x : List ℤ} {i : ℕ} (h : x.length ≤ i) : posFn x i = 0 := by
  unfold posFn
  rw [List.getD_eq_default _ _ h]
  simp

theorem negFn_eq_zero {y : List ℤ} {i : ℕ} (h : y.length ≤ i) : negFn y i = 0 := by
  unfold negFn
  exact posFn_eq_zero (by simpa using h)

theorem posFn_antitone {x : List ℤ} (h : x.Pairwise (· ≥ ·)) : Antitone (posFn x) := by
  intro i j hij
  by_cases hj : j < x.length
  · have hi : i < x.length := lt_of_le_of_lt hij hj
    simp only [posFn, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    apply Int.toNat_le_toNat
    rcases hij.lt_or_eq with hlt | heq
    · exact List.pairwise_iff_getElem.mp h i j hi hj hlt
    · subst heq
      exact le_rfl
  · rw [posFn_eq_zero (not_lt.mp hj)]
    exact Nat.zero_le _

theorem negFn_antitone {y : List ℤ} (h : y.Pairwise (· ≥ ·)) : Antitone (negFn y) := by
  show Antitone (posFn (y.reverse.map fun v => -v))
  apply posFn_antitone
  rw [List.pairwise_map, List.pairwise_reverse]
  exact h.imp fun hab => neg_le_neg hab

theorem posFn_cast {x : List ℤ} (hx : ∀ v ∈ x, 0 < v) {i : ℕ} (hi : i < x.length) :
    (posFn x i : ℚ) = (x[i] : ℤ) := by
  have hp : 0 < x[i] := hx _ (List.getElem_mem hi)
  simp only [posFn, List.getD_eq_getElem _ _ hi]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hp.le]

theorem negFn_cast {y : List ℤ} (hy : ∀ v ∈ y, v < 0) {i : ℕ} (hi : i < y.length) :
    (negFn y i : ℚ) = -((y[y.length - 1 - i] : ℤ) : ℚ) := by
  have hl : i < (y.reverse.map fun v => -v).length := by simpa using hi
  have hk : y.length - 1 - i < y.length := by omega
  have hv : y[y.length - 1 - i] < 0 := hy _ (List.getElem_mem hk)
  simp only [negFn, posFn, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_reverse]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]

theorem disj {x y : List ℤ} {n : ℕ} (h : x.length + y.length ≤ n) (i : Fin n) :
    posFn x i = 0 ∨ negFn y i.rev = 0 := by
  have hn := i.isLt
  by_cases hi : x.length ≤ (i : ℕ)
  · exact Or.inl (posFn_eq_zero hi)
  · right
    apply negFn_eq_zero
    rw [Fin.val_rev]
    omega

private lemma getD_map_intCast (l : List ℤ) (i : ℕ) :
    (l.map (fun v : ℤ => (v : ℚ))).getD i 0 = ((l.getD i 0 : ℤ) : ℚ) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

theorem pad_getD {x y : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0) {n : ℕ}
    (h : x.length + y.length ≤ n) (i : Fin n) :
    (pad x (n - x.length - y.length) y).getD i 0 = (posFn x i : ℚ) - negFn y i.rev := by
  have hn := i.isLt
  unfold pad
  rw [getD_map_intCast, List.append_assoc, Fin.val_rev]
  by_cases h1 : (i : ℕ) < x.length
  · rw [List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1, posFn_cast hx h1,
      negFn_eq_zero (by omega)]
    simp
  · rw [List.getD_append_right _ _ _ _ (not_lt.mp h1), posFn_eq_zero (not_lt.mp h1)]
    by_cases h2 : (i : ℕ) - x.length < n - x.length - y.length
    · rw [List.getD_append _ _ _ _ (by simpa using h2), negFn_eq_zero (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, h2]
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_replicate]
      have hj : n - ((i : ℕ) + 1) < y.length := by omega
      rw [negFn_cast hy hj]
      have e : (i : ℕ) - x.length - (n - x.length - y.length) = y.length - 1 - (n - ((i : ℕ) + 1)) := by
        omega
      rw [e, List.getD_eq_getElem _ _ (by omega)]
      simp

end GlobalTheory.JointHarm.ListShape

namespace GlobalTheory.JointHarm


open ListShape in
theorem fnShape_of_jointShape (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)
    (h : JointShape p q r s μ μ') : FnShape p q r s μ μ' := by
  obtain ⟨a, b, c, d, ha, hc, hb, hd, ha', hb', hc', hd', hab, hcd, had, hcb, hμ, hμ'⟩ := h
  refine ⟨posFn a, negFn b, posFn c, negFn d, posFn_antitone ha', negFn_antitone hb',
    posFn_antitone hc', negFn_antitone hd', fun i hi => posFn_eq_zero (by omega),
    fun i hi => negFn_eq_zero (by omega), fun i hi => posFn_eq_zero (by omega),
    fun i hi => negFn_eq_zero (by omega), disj hab, disj hcd, disj had, disj hcb,
    fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hμ]
    exact pad_getD ha hb hab i
  · rw [hμ]
    exact pad_getD hc hd hcd i
  · rw [hμ']
    exact pad_getD ha hd had i
  · rw [hμ']
    exact pad_getD hc hb hcb i

end GlobalTheory.JointHarm
end

section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm

theorem exists_length_of_antitone {α : ℕ → ℕ} (hα : Antitone α) {m : ℕ}
    (hm : ∀ i, m ≤ i → α i = 0) : ∃ t, t ≤ m ∧ ∀ i, α i = 0 ↔ t ≤ i := by
  classical
  have h : ∃ i, α i = 0 := ⟨m, hm m le_rfl⟩
  refine ⟨Nat.find h, Nat.find_min' h (hm m le_rfl), fun i => ⟨fun hi => Nat.find_min' h hi,
    fun hi => ?_⟩⟩
  have := hα hi
  rw [Nat.find_spec h] at this
  exact Nat.le_zero.1 this

theorem length_add_le_of_disjoint {α β : ℕ → ℕ} {t u n : ℕ} (ht : ∀ i, α i = 0 ↔ t ≤ i)
    (hu : ∀ i, β i = 0 ↔ u ≤ i) (htn : t ≤ n) (hun : u ≤ n)
    (h : ∀ i : Fin n, α i = 0 ∨ β i.rev = 0) : t + u ≤ n := by
  by_contra hc
  have h1 := h ⟨t - 1, by omega⟩
  rw [ht, hu, Fin.val_rev] at h1
  simp only at h1
  omega

def posList (α : ℕ → ℕ) (t : ℕ) : List ℤ := (List.range t).map fun i => (α i : ℤ)

def negList (β : ℕ → ℕ) (t : ℕ) : List ℤ := ((List.range t).map fun i => -(β i : ℤ)).reverse

@[simp] theorem length_posList (α : ℕ → ℕ) (t : ℕ) : (posList α t).length = t := by
  simp [posList]

@[simp] theorem length_negList (β : ℕ → ℕ) (t : ℕ) : (negList β t).length = t := by
  simp [negList]

theorem posList_pos {α : ℕ → ℕ} {t : ℕ} (ht : ∀ i, α i = 0 ↔ t ≤ i) :
    ∀ v ∈ posList α t, 0 < v := by
  intro v hv
  simp only [posList, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have := ht i
  omega

theorem negList_neg {β : ℕ → ℕ} {t : ℕ} (ht : ∀ i, β i = 0 ↔ t ≤ i) :
    ∀ v ∈ negList β t, v < 0 := by
  intro v hv
  simp only [negList, List.mem_reverse, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have := ht i
  omega

theorem posList_pairwise {α : ℕ → ℕ} (hα : Antitone α) (t : ℕ) :
    (posList α t).Pairwise (· ≥ ·) := by
  rw [posList, List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {a b} h => ?_
  have := hα h.le
  omega

theorem negList_pairwise {β : ℕ → ℕ} (hβ : Antitone β) (t : ℕ) :
    (negList β t).Pairwise (· ≥ ·) := by
  rw [negList, List.pairwise_reverse, List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {a b} h => ?_
  have := hβ h.le
  omega

theorem getD_pad_posList_negList {α β : ℕ → ℕ} {t u n : ℕ} (ht : ∀ i, α i = 0 ↔ t ≤ i)
    (hu : ∀ i, β i = 0 ↔ u ≤ i) (hn : t + u ≤ n) (i : Fin n) :
    (pad (posList α t) (n - (posList α t).length - (negList β u).length) (negList β u)).getD i 0
      = (α i : ℚ) - β i.rev := by
  obtain ⟨i, hi⟩ := i
  simp only [length_posList, length_negList, Fin.val_rev]
  have hlen : i < (pad (posList α t) (n - t - u) (negList β u)).length := by
    simp [pad]; omega
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [pad, List.getElem_map, List.getElem_append, List.length_append, length_posList,
    List.length_replicate, List.getElem_replicate]
  split_ifs with h1 h2
  · rw [(hu _).2 (by omega)]
    simp [posList]
  · rw [(hu _).2 (by omega), (ht _).2 (by omega)]
    simp
  · rw [(ht _).2 (by omega)]
    simp only [negList, List.getElem_reverse, List.getElem_map, List.getElem_range,
      List.length_map, List.length_range]
    have : u - 1 - (i - (t + (n - t - u))) = n - (i + 1) := by omega
    rw [this]
    simp

theorem jointShape_of_fnShape (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)
    (h : FnShape p q r s μ μ') : JointShape p q r s μ μ' := by
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, zα, zβ, zγ, zδ, d1, d2, d3, d4, e1, e2, e3, e4⟩ := h
  obtain ⟨a, ha, ta⟩ := exists_length_of_antitone hα zα
  obtain ⟨b, hb, tb⟩ := exists_length_of_antitone hβ zβ
  obtain ⟨c, hc, tc⟩ := exists_length_of_antitone hγ zγ
  obtain ⟨d, hd, td⟩ := exists_length_of_antitone hδ zδ
  rw [le_min_iff] at ha hb hc hd
  have l1 := length_add_le_of_disjoint ta tb ha.1 hb.1 d1
  have l2 := length_add_le_of_disjoint tc td hc.1 hd.1 d2
  have l3 := length_add_le_of_disjoint ta td ha.2 hd.2 d3
  have l4 := length_add_le_of_disjoint tc tb hc.2 hb.2 d4
  refine ⟨posList α a, negList β b, posList γ c, negList δ d, posList_pos ta, posList_pos tc,
    negList_neg tb, negList_neg td, posList_pairwise hα a, negList_pairwise hβ b,
    posList_pairwise hγ c, negList_pairwise hδ d, by simpa using l1, by simpa using l2,
    by simpa using l3, by simpa using l4, ?_, ?_⟩
  · funext x
    rcases x with i | i
    · exact (e1 i).trans (getD_pad_posList_negList ta tb l1 i).symm
    · exact (e2 i).trans (getD_pad_posList_negList tc td l2 i).symm
  · funext x
    rcases x with i | i
    · exact (e3 i).trans (getD_pad_posList_negList ta td l3 i).symm
    · exact (e4 i).trans (getD_pad_posList_negList tc tb l4 i).symm

end GlobalTheory.JointHarm
end

section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm

theorem sum_Ici_sub_succ {n : ℕ} (α : ℕ → ℕ) (hα : Antitone α) (h0 : α n = 0) (a : Fin n) :
    ∑ i ∈ Finset.Ici a, (α (i : ℕ) - α ((i : ℕ) + 1)) = α a := by
  have key : ∀ k, ∑ i ∈ Finset.Ico (a : ℕ) (a + k), (α i - α (i + 1)) + α (a + k) = α a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
      have := hα (Nat.le_succ (a + k))
      simp only [Nat.succ_eq_add_one] at this
      omega
  have h1 := key (n - a)
  rw [show (a : ℕ) + (n - a) = n by have := a.2; omega, h0, add_zero] at h1
  rw [← h1]
  refine Finset.sum_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Ici, Fin.le_def] at hi
    exact Finset.mem_Ico.2 ⟨hi, i.2⟩
  · intro i _ j _ h
    exact Fin.ext h
  · intro b hb
    rw [Finset.mem_Ico] at hb
    exact ⟨⟨b, hb.2⟩, Finset.mem_Ici.2 (Fin.le_def.2 hb.1), rfl⟩
  · intro _ _
    rfl

theorem exists_eq_mul_minorPoly (σ : Type) [DecidableEq σ] (p r : ℕ) (z : Fin p × Fin r → σ)
    (hz : Function.Injective z) (α : ℕ → ℕ) (hα : Antitone α) (h0 : ∀ i, min p r ≤ i → α i = 0)
    (P : MvPolynomial σ ℂ) (hP : BlockHW z α P) :
    ∃ Q : MvPolynomial σ ℂ, (∀ w, z w ∉ Q.vars) ∧ P = Q * minorPoly z α := by
  by_cases hP0 : P = 0
  · exact ⟨0, by simp, by simp [hP0]⟩
  obtain ⟨hru, hcu, hrw, hcw⟩ := hP
  have hrow : ∀ a : Fin p, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = α a := fun a m hm => by
    exact_mod_cast (rowOp_eq_smul_iff z a P _).1 (hrw a) m hm
  have hcol : ∀ k : Fin r, ∀ m ∈ P.support, ∑ a, m (z (a, k)) = α k := fun k m hm => by
    exact_mod_cast (colOp_eq_smul_iff z k P _).1 (hcw k) m hm
  let e : Fin (min p r) → Fin p := Fin.castLE (min_le_left p r)
  let f : Fin (min p r) → Fin r := Fin.castLE (min_le_right p r)
  have hei : Function.Injective e := Fin.castLE_injective _
  have hfi : Function.Injective f := Fin.castLE_injective _
  have hve : ∀ a k, a ∉ Set.range e → z (a, k) ∉ P.vars := by
    intro a k ha hv
    obtain ⟨m, hm, hv⟩ := (mem_vars_iff_mem_support _).1 hv
    have h1 := hrow a m hm
    rw [h0 a (not_lt.1 fun h' => ha ⟨⟨a, h'⟩, rfl⟩), Finset.sum_eq_zero_iff] at h1
    exact Finsupp.mem_support_iff.1 hv (h1 k (Finset.mem_univ _))
  have hvf : ∀ a k, k ∉ Set.range f → z (a, k) ∉ P.vars := by
    intro a k hk hv
    obtain ⟨m, hm, hv⟩ := (mem_vars_iff_mem_support _).1 hv
    have h1 := hcol k m hm
    rw [h0 k (not_lt.1 fun h' => hk ⟨⟨k, h'⟩, rfl⟩), Finset.sum_eq_zero_iff] at h1
    exact Finsupp.mem_support_iff.1 hv (h1 a (Finset.mem_univ _))
  obtain ⟨Q, hQ, hPQ⟩ := eq_mul_prod_minors (fun w : Fin (min p r) × Fin (min p r) =>
      z (e w.1, f w.2)) (hz.comp (hei.prodMap hfi)) P (fun i => α i - α (i + 1))
    (fun a m hm => by
      rw [sum_Ici_sub_succ α hα (h0 _ le_rfl)]
      refine Eq.trans ?_ (hrow (e a) m hm)
      refine Fintype.sum_of_injective f hfi _ _ (fun k hk => ?_) fun _ => rfl
      by_contra h1
      exact hvf _ k hk ((mem_vars_iff_mem_support _).2 ⟨m, hm, Finsupp.mem_support_iff.2 h1⟩))
    (fun i j hij => by
      have h₁ := (rowOp_apply _ _ _ _).symm.trans (hru (e i) (e j) hij)
      refine ((rowAdd_invariant_iff (fun k => z (e i, f k)) (fun k => z (e j, f k))
        (fun k l h => hfi (by simpa using hz h))
        (fun k l h => hij.ne (hei (congrArg Prod.fst (hz h)))) P).out 3 2).1 (Eq.trans ?_ h₁)
      refine Fintype.sum_of_injective f hfi _ _ (fun k hk => ?_) fun _ => rfl
      rw [pderiv_eq_zero_of_notMem_vars (hvf _ k hk), mul_zero])
    (fun i j hij => by
      have h₁ := (colOp_apply _ _ _ _).symm.trans (hcu (f i) (f j) hij)
      refine ((rowAdd_invariant_iff (fun k => z (e k, f i)) (fun k => z (e k, f j))
        (fun k l h => hei (by simpa using hz h))
        (fun k l h => hij.ne (hfi (congrArg Prod.snd (hz h)))) P).out 3 2).1 (Eq.trans ?_ h₁)
      refine Fintype.sum_of_injective e hei _ _ (fun k hk => ?_) fun _ => rfl
      rw [pderiv_eq_zero_of_notMem_vars (hve k _ hk), mul_zero])
  have hPQ' : P = Q * minorPoly z α := hPQ
  refine ⟨Q, ?_, hPQ'⟩
  have hsub : ∀ s ∈ Q.vars, s ∈ P.vars := by
    intro s hs
    rw [mem_vars_iff_degreeOf_ne_zero] at hs ⊢
    rw [hPQ'] at hP0 ⊢
    rw [degreeOf_mul_eq (left_ne_zero_of_mul hP0) (right_ne_zero_of_mul hP0)]
    omega
  rintro ⟨a, k⟩ hw
  by_cases ha : a ∈ Set.range e
  · by_cases hk : k ∈ Set.range f
    · obtain ⟨a, rfl⟩ := ha
      obtain ⟨k, rfl⟩ := hk
      exact hQ (a, k) hw
    · exact hvf a k hk (hsub _ hw)
  · exact hve a k ha (hsub _ hw)

end GlobalTheory.JointHarm
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.relIndex_conj_uniformizerPowerDiagonalGL_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (σ : n ≃ n') (e : n → ℤ),
    ((KO k n').map (MulAut.conj (torusElt k n' ϖ (e ∘ σ.symm))).toMonoidHom).relIndex (KO k n') =
      ((KO k n).map (MulAut.conj (torusElt k n ϖ e)).toMonoidHom).relIndex (KO k n) :=
  GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.FockKFin

theorem sameBlock_iff_isLeft {p q : ℕ} (a b : Ix p q) : sameBlock a b ↔ a.isLeft = b.isLeft := by
  cases a <;> cases b <;> simp [sameBlock]

theorem isKC_one {p q : ℕ} : IsKC (1 : Mat p q) := by
  intro a b h
  apply Matrix.one_apply_ne
  rintro rfl
  exact h ((sameBlock_iff_isLeft a a).2 rfl)

theorem isKC_kronecker {p q r s : ℕ} (A : Mat p q) (B : Mat r s) (hA : IsKC A) (hB : IsKC B) :
    IsKC (Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      (Matrix.kroneckerMap (· * ·) A B)) := by
  intro x y hxy
  obtain ⟨⟨a, c⟩, rfl⟩ := (lineEquiv p q r s).surjective x
  obtain ⟨⟨b, d⟩, rfl⟩ := (lineEquiv p q r s).surjective y
  rw [sameBlock_iff_isLeft, lineEquiv_isLeft, lineEquiv_isLeft] at hxy
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply]
  by_cases h1 : sameBlock a b
  · by_cases h2 : sameBlock c d
    · exfalso
      apply hxy
      cases a <;> cases b <;> cases c <;> cases d <;> simp_all [sameBlock, linePos]
    · rw [hB c d h2, mul_zero]
  · rw [hA a b h1, zero_mul]

theorem emb_mem_Kset {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)}
    {T1 : GrpData p q} {T2 : GrpData r s} (F : FockData T0 T1 T2) {g : T1.G} {h : T2.G}
    (hg : g ∈ T1.Kset) (hh : h ∈ T2.Kset) : F.emb (g, h) ∈ T0.Kset := by
  change IsKC _
  rw [F.emb_cov]
  exact isKC_kronecker _ _ hg hh

theorem one_mem_Kset {p q : ℕ} (T : GrpData p q) : (1 : T.G) ∈ T.Kset := by
  change IsKC _
  rw [map_one, Units.val_one]
  exact isKC_one

theorem exists_finite {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)}
    {T1 : GrpData p q} {T2 : GrpData r s} (F : FockData T0 T1 T2)
    (H : ∀ k ∈ T0.Kset, ∀ (d : ℕ), ∀ P ∈ homog (Ix p q × Ix r s) d,
      ∃ Q ∈ homog (Ix p q × Ix r s) d, F.Om k (F.ι P) = F.ι Q) (P : Pol p q r s) :
    ∃ W : Submodule ℂ F.H, FiniteDimensional ℂ W ∧ ∀ k ∈ T0.Kset, F.Om k (F.ι P) ∈ W := by
  refine ⟨(MvPolynomial.restrictTotalDegree (Ix p q × Ix r s) ℂ P.totalDegree).map F.ι,
    inferInstance, fun k hk => ?_⟩
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent P]

  rw [map_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  obtain ⟨Q, hQ, e⟩ := H k hk d _ (MvPolynomial.homogeneousComponent_mem d P)
  rw [e]
  refine Submodule.mem_map_of_mem ?_
  rw [MvPolynomial.mem_restrictTotalDegree]
  have h1 : Q.totalDegree ≤ d := MvPolynomial.IsHomogeneous.totalDegree_le hQ
  have h2 := Finset.mem_range.1 hd
  omega

theorem kfin_fock : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), (∀ k ∈ T0.Kset, ∀ (d : ℕ), ∀ P ∈ homog (Ix p q × Ix r s) d, ∃ Q ∈ homog (Ix p q × Ix r s) d, F.Om k (F.ι P) = F.ι Q) → ∀ P : Pol p q r s, KFin T1 (fun g => F.π (g, 1)) (F.ι P) ∧ KFin T2 (fun h => F.π (1, h)) (F.ι P) := by
  intro p q r s T0 T1 T2 F H P
  obtain ⟨W, hW, hmem⟩ := exists_finite F H P
  constructor
  · refine Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact hmem _ (emb_mem_Kset F k.2 (one_mem_Kset T2))
  · refine Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact hmem _ (emb_mem_Kset F (one_mem_Kset T1) k.2)

end GlobalTheory.FockKFin
end
