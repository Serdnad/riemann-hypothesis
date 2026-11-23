module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
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
import Mathlib.Data.Finsupp.Pointwise
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.SeqCx

namespace GlobalTheory.SeqCx.ColDecomp

lemma inj_pair {V W : Type} (l : List V) : Function.Injective (fun w : List W => (l, w)) := by
  intro u v h
  exact (Prod.mk.inj h).2

open Classical in
lemma sum_apply_pair {V W : Type} (T : Finset (List V)) (g : List V → List W →₀ ℤ) (l : List V) (w : List W) :
    (∑ l' ∈ T, Finsupp.mapDomain (fun w => (l', w)) (g l')) (l, w) = if l ∈ T then g l w else 0 := by
  rw [Finsupp.finsetSum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single l]
    · exact Finsupp.mapDomain_apply_of_injective (inj_pair l) _ _
    · intro l' _ hne
      apply Finsupp.mapDomain_notin_range
      rintro ⟨w', hw'⟩
      exact hne (congrArg Prod.fst hw')
    · intro hl
      exact absurd h hl
  · apply Finset.sum_eq_zero
    intro l' hl'
    apply Finsupp.mapDomain_notin_range
    rintro ⟨w', hw'⟩
    obtain rfl : l' = l := congrArg Prod.fst hw'
    exact h hl'

lemma vbd_mapDomain {V W : Type} (l : List V) (c : List W →₀ ℤ) :
    vbd V W (Finsupp.mapDomain (fun w => (l, w)) c) = Finsupp.mapDomain (fun w => (l, w)) (bd W c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add (f := _), hf, hg, map_add (f := _), Finsupp.mapDomain_add]
  | single w k =>
    rw [Finsupp.mapDomain_single]
    simp only [vbd, bd, Finsupp.linearCombination_single]
    rw [one_smul, Finsupp.mapDomain_smul]

end GlobalTheory.SeqCx.ColDecomp


open GlobalTheory.SeqCx.ColDecomp in
theorem GlobalTheory.SeqCx.vertical_exact_of_columns : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ), (∀ l : List V, l.length = a → (∃ w, (l, w) ∈ D) → ExactAt {w | (l, w) ∈ D} b) → ∀ x ∈ chains2 D a b, vbd V W x = 0 → ∃ y ∈ chains2 D a (b + 1), vbd V W y = x := by
  classical
  intro V W D a b hex x hx hvx
  set T : Finset (List V) := x.support.image Prod.fst with hT
  set g : List V → List W →₀ ℤ := fun l => x.curry l with hg
  have hgapp : ∀ l w, g l w = x (l, w) := fun l w => Finsupp.curry_apply x l w
  have hsupp : ∀ z ∈ x.support, z ∈ D ∧ z.1.length = a ∧ z.2.length = b := fun z hz => hx hz
  have hdec : x = ∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (g l) := by
    ext ⟨l, w⟩
    rw [sum_apply_pair]
    split_ifs with h
    · rw [hgapp]
    · by_contra hne
      exact h (Finset.mem_image.2 ⟨(l, w), Finsupp.mem_support_iff.2 hne, rfl⟩)
  have hvdec : vbd V W x = ∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (bd W (g l)) := by
    conv_lhs => rw [hdec]

    rw [map_sum]
    exact Finset.sum_congr rfl (fun l _ => vbd_mapDomain l (g l))
  have hcyc : ∀ l ∈ T, bd W (g l) = 0 := by
    intro l hl
    ext w
    have := congrArg (fun f => f (l, w)) hvdec
    simp only [hvx, sum_apply_pair, if_pos hl] at this
    simpa using this.symm
  have hchain : ∀ l ∈ T, g l ∈ chains {w | (l, w) ∈ D} b := by
    intro l hl
    rw [chains, Finsupp.mem_supported]
    intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hgapp] at hw
    have := hsupp (l, w) (Finsupp.mem_support_iff.2 hw)
    exact ⟨this.1, this.2.2⟩
  have hpre : ∀ l ∈ T, l.length = a ∧ ∃ w, (l, w) ∈ D := by
    intro l hl
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hl
    have := hsupp z hz
    exact ⟨this.2.1, z.2, this.1⟩
  have hy : ∀ l ∈ T, ∃ y ∈ chains {w | (l, w) ∈ D} (b + 1), bd W y = g l := by
    intro l hl
    exact hex l (hpre l hl).1 (hpre l hl).2 (g l) (hchain l hl) (hcyc l hl)
  choose! y hymem hybd using hy
  refine ⟨∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (y l), ?_, ?_⟩
  · refine Submodule.sum_mem _ (fun l hl => ?_)
    rw [chains2, Finsupp.mem_supported]
    intro z hz
    have hz' := Finsupp.mapDomain_support (Finset.mem_coe.1 hz)
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz'
    have hyl := hymem l hl
    rw [chains, Finsupp.mem_supported] at hyl
    have := hyl (Finset.mem_coe.2 hw)
    exact ⟨this.1, (hpre l hl).1, this.2⟩

  · rw [map_sum, hdec]
    exact Finset.sum_congr rfl (fun l hl => by rw [vbd_mapDomain, hybd l hl])

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pairSeqVerticalCycle_is_boundary_of_slices_exact : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ), (∀ l : List V, l.length = a → (∃ w, (l, w) ∈ D) → ExactAt {w | (l, w) ∈ D} b) → ∀ x ∈ chains2 D a b, vbd V W x = 0 → ∃ y ∈ chains2 D a (b + 1), vbd V W y = x := by
  first
  | exact @GlobalTheory.SeqCx.vertical_exact_of_columns
end
end

section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem splitPairs_subClosed2 : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed2 (splitPairs R n) := by
  intro R _ n z hz x w hx hw
  obtain ⟨h1, h2, h3⟩ := hz
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hw
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [hf i, hf j, h1 (f i) (f j)]
    simp only [f.eq_iff_eq]
  · obtain ⟨F, hF⟩ := h2
    refine ⟨fun i => F (g i), fun i j => ?_⟩
    rw [hg j, hF]
    simp only [g.eq_iff_eq]
  · intro y hy u hu
    exact h3 y (hx.subset hy) u (hw.subset hu)

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.subClosed2_splitPairs : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed2 (splitPairs R n) := by
  first
  | exact @GlobalTheory.SeqCx.splitPairs_subClosed2
end
end

section

open GlobalTheory.SeqCx

namespace GlobalTheory.SeqCx.DblBd

theorem single_eq_smul {α : Type} (a : α) (r : ℤ) :
    Finsupp.single a r = r • Finsupp.single a (1 : ℤ) := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem hbd_single (V W : Type) (z : List V × List W) :
    hbd V W (Finsupp.single z 1) =
      ∑ i ∈ Finset.range z.1.length, (-1 : ℤ) ^ i • Finsupp.single (z.1.eraseIdx i, z.2) (1 : ℤ) := by
  simp only [hbd, bd, Finsupp.linearCombination_single, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single, one_smul]

theorem vbd_single (V W : Type) (z : List V × List W) :
    vbd V W (Finsupp.single z 1) =
      ∑ j ∈ Finset.range z.2.length, (-1 : ℤ) ^ j • Finsupp.single (z.1, z.2.eraseIdx j) (1 : ℤ) := by
  simp only [vbd, bd, Finsupp.linearCombination_single, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single, one_smul]

theorem hbd_mapDomain (V W : Type) (w : List W) (c : List V →₀ ℤ) :
    hbd V W (Finsupp.mapDomain (fun x => (x, w)) c) = Finsupp.mapDomain (fun x => (x, w)) (bd V c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add (f := _), hf, hg, map_add (f := _), Finsupp.mapDomain_add]
  | single l r =>
    rw [Finsupp.mapDomain_single, single_eq_smul, map_zsmul, single_eq_smul l r, map_zsmul,
      Finsupp.mapDomain_smul]
    simp [hbd, Finsupp.linearCombination_single]

theorem vbd_mapDomain (V W : Type) (x : List V) (c : List W →₀ ℤ) :
    vbd V W (Finsupp.mapDomain (fun w => (x, w)) c) = Finsupp.mapDomain (fun w => (x, w)) (bd W c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add (f := _), hf, hg, map_add (f := _), Finsupp.mapDomain_add]
  | single l r =>
    rw [Finsupp.mapDomain_single, single_eq_smul, map_zsmul, single_eq_smul l r, map_zsmul,
      Finsupp.mapDomain_smul]
    simp [vbd, Finsupp.linearCombination_single]

theorem hbd_hbd (V W : Type) (x : List V × List W →₀ ℤ) : hbd V W (hbd V W x) = 0 := by
  have h : hbd V W ∘ₗ hbd V W = 0 := by
    apply Finsupp.lhom_ext
    intro z r
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [single_eq_smul, map_zsmul, map_zsmul]
    have e : hbd V W (Finsupp.single z 1) =
        Finsupp.mapDomain (fun x => (x, z.2)) (bd V (Finsupp.single z.1 1)) := by
      simp [hbd, Finsupp.linearCombination_single]
    rw [e, hbd_mapDomain, bd_bd, Finsupp.mapDomain_zero, smul_zero]
  exact congrArg (fun f => f x) h

theorem vbd_vbd (V W : Type) (x : List V × List W →₀ ℤ) : vbd V W (vbd V W x) = 0 := by
  have h : vbd V W ∘ₗ vbd V W = 0 := by
    apply Finsupp.lhom_ext
    intro z r
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [single_eq_smul, map_zsmul, map_zsmul]
    have e : vbd V W (Finsupp.single z 1) =
        Finsupp.mapDomain (fun w => (z.1, w)) (bd W (Finsupp.single z.2 1)) := by
      simp [vbd, Finsupp.linearCombination_single]
    rw [e, vbd_mapDomain, bd_bd, Finsupp.mapDomain_zero, smul_zero]
  exact congrArg (fun f => f x) h

theorem hbd_vbd (V W : Type) (x : List V × List W →₀ ℤ) : hbd V W (vbd V W x) = vbd V W (hbd V W x) := by
  have h : hbd V W ∘ₗ vbd V W = vbd V W ∘ₗ hbd V W := by
    apply Finsupp.lhom_ext
    intro z r
    simp only [LinearMap.comp_apply]
    rw [single_eq_smul, map_zsmul, map_zsmul, map_zsmul, map_zsmul]
    congr 1

    rw [vbd_single, hbd_single, map_sum, map_sum]
    simp only [map_zsmul, hbd_single, vbd_single, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  exact congrArg (fun f => f x) h

end GlobalTheory.SeqCx.DblBd

namespace GlobalTheory.SeqCx

theorem dbl_bd : ∀ (V W : Type), (∀ x, hbd V W (hbd V W x) = 0) ∧ (∀ x, vbd V W (vbd V W x) = 0) ∧
    (∀ x, hbd V W (vbd V W x) = vbd V W (hbd V W x)) :=
  fun V W => ⟨DblBd.hbd_hbd V W, DblBd.vbd_vbd V W, DblBd.hbd_vbd V W⟩

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pairSeqDoubleComplex_boundary_relations : ∀ (V W : Type), (∀ x, hbd V W (hbd V W x) = 0) ∧ (∀ x, vbd V W (vbd V W x) = 0) ∧ (∀ x, hbd V W (vbd V W x) = vbd V W (hbd V W x)) := by
  first
  | exact @GlobalTheory.SeqCx.dbl_bd
end
end

section

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

theorem finsupp_coord_ideal_eq_top {R : Type} [CommRing R] (u : ℕ →₀ R) (g : (ℕ →₀ R) →ₗ[R] R)
    (hg : g u = 1) (K : Ideal R) (hK : ∀ i, u i ∈ K) : K = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← hg]
  rw [show g u = g (u.sum Finsupp.single) by rw [Finsupp.sum_single]]

  rw [Finsupp.sum, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (hK i)

theorem finsupp_exists_form_of_span {R : Type} [CommRing R] (u : ℕ →₀ R)
    (h : Ideal.span (Set.range fun i => u i) = ⊤) : ∃ g : (ℕ →₀ R) →ₗ[R] R, g u = 1 := by
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun i => u i) := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h1
  refine ⟨∑ i ∈ c.support, c i • Finsupp.lapply i, ?_⟩
  rw [← hc]
  simp [Finsupp.sum, LinearMap.sum_apply]

private theorem linearMap_apply_mem_span_range_coeffs {R : Type} [CommRing R] (w : ℕ →₀ R)
    (g : (ℕ →₀ R) →ₗ[R] R) : g w ∈ Ideal.span (Set.range fun i => w i) := by
  have e : g w = ∑ i ∈ w.support, w i * g (Finsupp.single i 1) := by
    conv_lhs => rw [← Finsupp.sum_single w]

    rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
  rw [e]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem unimodular_partner_aff : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n j : ℕ), s ≤ n →
    n ≤ j → ∀ v : ℕ →₀ R, [v] ∈ uniM R (ℕ →₀ R) → ∃ x ∈ aff R n j, [v, x] ∈ uniM R (ℕ →₀ R) := by
  intro R _ s hs n j hsn hnj v hv
  obtain ⟨f, hf⟩ := hv
  obtain ⟨f0, hf0⟩ : ∃ f0 : (ℕ →₀ R) →ₗ[R] R, f0 v = 1 :=
    ⟨f ⟨0, by simp⟩, by simpa using hf ⟨0, by simp⟩ ⟨0, by simp⟩⟩
  let a : ℕ → R := fun i => f0 (Finsupp.single i 1)
  let φ : (ℕ →₀ R) →ₗ[R] R :=
    f0 - ∑ i ∈ Finset.range n, a i • Finsupp.lapply i - a j • Finsupp.lapply j
  have hφ : ∀ w, φ w = f0 w - ∑ i ∈ Finset.range n, a i * w i - a j * w j := by
    intro w
    simp [φ, LinearMap.sum_apply]
  have hφs : ∀ k c, k < n → φ (Finsupp.single k c) = 0 := by
    intro k c hk
    have h1 : f0 (Finsupp.single k c) = c * a k := by
      rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
    rw [hφ, h1, Finset.sum_eq_single k
      (fun b _ hb => by simp [Finsupp.single_apply, Ne.symm hb])
      (fun h => absurd (Finset.mem_range.2 hk) h)]
    simp only [Finsupp.single_eq_same, Finsupp.single_apply, if_neg (show k ≠ j by omega), mul_zero,
      sub_zero]
    ring
  have hφj : φ (Finsupp.single j 1) = 0 := by
    rw [hφ, Finset.sum_eq_zero (fun i hi => by
      have := Finset.mem_range.1 hi
      simp [Finsupp.single_apply, show j ≠ i by omega])]
    simp [a]
  let b' : R := φ v + a j * v j
  let r : Fin (n + 1) → R := fun i => if (i : ℕ) < n then v i else b'
  have hrc : ∀ i : Fin n, r i.castSucc = v i := fun i => by simp [r, i.isLt]
  have hrl : r (Fin.last n) = b' := by simp [r]
  have hr : Unimodular R r := by
    show Ideal.span (Set.range r) = ⊤
    rw [Ideal.eq_top_iff_one]
    have key : (1 : R) = ∑ i : Fin n, a i * r i.castSucc + 1 * r (Fin.last n) := by
      simp only [hrc, hrl, one_mul, b']
      rw [hφ, ← hf0, ← Finset.sum_range (fun i => a i * v i)]
      ring
    rw [key]
    exact Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨t, ht⟩ := hs n hsn r hr
  have ht' : Ideal.span (Set.range fun i => r i.castSucc + t i * r (Fin.last n)) = ⊤ := ht
  let y : ℕ →₀ R := ∑ i : Fin n, Finsupp.single (i : ℕ) (-(t i * a j))
  have hy0 : ∀ m, n ≤ m → y m = 0 := by
    intro m hm
    simp only [y, Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun i _ => by
      have := i.isLt
      simp [Finsupp.single_apply, show (i : ℕ) ≠ m by omega]
  have hyi : ∀ i : Fin n, y i = -(t i * a j) := by
    intro i
    simp only [y, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, Fin.val_ne_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  let x : ℕ →₀ R := Finsupp.single j 1 + y
  have hxj : x j = 1 := by simp [x, hy0 j hnj]
  have hxaff : x ∈ aff R n j := by
    simp only [aff, low, Set.mem_setOf_eq]
    intro m hm
    simp [x, hy0 m hm]
  have hφx : φ x = 0 := by

    simp only [x, map_add (f := _), hφj, zero_add, y, map_sum]
    exact Finset.sum_eq_zero fun i _ => hφs _ _ i.isLt
  let v' : ℕ →₀ R := v - v j • x
  have hv'i : ∀ i : Fin n, v' i = v i + v j * (t i * a j) := by
    intro i
    simp only [v', x, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply, hyi,
      Finsupp.single_apply, if_neg (show j ≠ (i : ℕ) by have := i.isLt; omega)]
    ring
  have hφv' : φ v' = φ v := by simp [v', hφx]
  have hspan : Ideal.span (Set.range fun i => v' i) = ⊤ := by
    rw [eq_top_iff, ← ht', Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have he : r i.castSucc + t i * r (Fin.last n) = v' i + t i * φ v' := by
      rw [hrc, hrl, hv'i, hφv']
      simp only [b']
      ring
    simp only [he]
    exact Ideal.add_mem _ (Ideal.subset_span ⟨(i : ℕ), rfl⟩)
      (Ideal.mul_mem_left _ _ (linearMap_apply_mem_span_range_coeffs v' φ))
  obtain ⟨h, hh⟩ := finsupp_exists_form_of_span v' hspan
  let f1 : (ℕ →₀ R) →ₗ[R] R := h - h x • Finsupp.lapply j
  let f2 : (ℕ →₀ R) →ₗ[R] R := Finsupp.lapply j - v j • f1
  have hvdec : v = v' + v j • x := by simp [v']
  have hhv : h v = 1 + v j * h x := by
    conv_lhs => rw [hvdec]
    rw [map_add (f := _), map_smul, hh, smul_eq_mul]
  have hf1x : f1 x = 0 := by
    simp only [f1, LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, hxj]
    ring
  have hf1v : f1 v = 1 := by
    simp only [f1, LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, hhv]
    ring
  have hf2x : f2 x = 1 := by
    simp only [f2, LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, hf1x, hxj]
    ring
  have hf2v : f2 v = 0 := by
    simp only [f2, LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, hf1v]
    ring
  refine ⟨x, hxaff, ?_⟩
  simp only [uniM, Set.mem_setOf_eq]
  refine ⟨![f1, f2], ?_⟩
  intro p q
  fin_cases p <;> fin_cases q <;> simp [hf1x, hf1v, hf2x, hf2v]

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_mem_translate_unimodular_pair_of_stableRangeLe : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n j : ℕ), s ≤ n → n ≤ j → ∀ v : ℕ →₀ R, [v] ∈ uniM R (ℕ →₀ R) → ∃ x ∈ aff R n j, [v, x] ∈ uniM R (ℕ →₀ R) := by
  first
  | exact @GlobalTheory.unimodular_partner_aff
  | exact @GlobalTheory.finsupp_exists_form_of_span
  | exact @GlobalTheory.finsupp_coord_ideal_eq_top
end
end
