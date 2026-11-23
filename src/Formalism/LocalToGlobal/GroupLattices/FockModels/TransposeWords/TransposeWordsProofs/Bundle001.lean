module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockPairingHighestWeight
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LEhwLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle004
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle011
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

theorem hw_dom {B : Type} [CommRing B] [IsDomain B] {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r)
    (f : MvPolynomial (Fin r × Fin n) B) (hf : f ∈ dualWeyl B r n ν) :
    ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a := by
  classical
  rw [standardMonomialSpanDomain B r n ν] at hf
  have key : ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t := by
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
      intro m hm k
      have h := (bidetDominance B r n K sz hsz I m hm).1 k
      rw [hshape] at h
      exact h
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm
      rcases Finset.mem_union.mp (support_add hm) with h | h
      · exact hx m h
      · exact hy m h
    | smul c x _ hx =>
      intro m hm
      exact hx m (support_smul hm)
  intro m hm k
  rw [rowNu_partial_sum ν hnr k]
  exact key m hm k

theorem hw_kill {B : Type} [CommRing B] [IsDomain B] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (G : MvPolynomial (Fin r × Fin n) B) (hG : G ∈ dualWeyl B r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv B a b k G = 0 := by
  classical
  have hGp : IsWeightedHomogeneous (lehwP a) G
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by
    intro m hm
    rw [lehw_weight_P]
    have hm' := hGh hm
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← lehw_weight_rowW, hm']
  have hsh := lehw_rowDiv_shift B (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGp
  have hmem := rowDivStable B r n ν a b k G hG
  by_contra hne
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hne
  have h1 := hsh hm
  rw [lehw_weight_P] at h1
  have h2 := hw_dom ν hn _ hmem m (mem_support_iff.mpr hm) (a.val + 1)
  have h3 : ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) ≤
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by exact_mod_cast h2
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  rw [h1] at h3
  linarith

theorem eval_idFrame_hw (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame R r n) (hw R hn ν) = 1 := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow]
  have h := eval_idPoint_lpMinor R (r := r) (n := n) (s.val + 1) (by omega) (by omega)
  change eval (idPoint R r n) _ ^ _ = 1
  rw [h, one_pow]

theorem fock_pairing_highest_weight_proof : FockPairingHighestWeight := by
  intro K _ _ r n hn ν hν F hF
  classical
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F with hGdef
  have hG : G ∈ dualWeyl K r n ν := dualWeylRowGraded K r n ν _ F hF
  have hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν) :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨c, hc⟩ := hwLine K r n hn ν hν G hG
    (fun a b hab k hk => hw_kill hn ν G hG hGh a b hab k hk)
  have hHW := hwRowWeight K r n hn ν hν
  have h1 : fockR (hw K hn ν) F = fockR (hw K hn ν) G := by
    unfold fockR
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hm))]
  have h2 : fockR (hw K hn ν) G = c * fockR (hw K hn ν) (hw K hn ν) := by
    rw [hc]
    unfold fockR
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    ring
  have hcolF : IsWeightedHomogeneous (colW r n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1
  have hcolH : IsWeightedHomogeneous (colW r n) (hw K hn ν) ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp (hwMem K r n hn ν hν)).1
  have hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → idFrame K r n (a, j) = 0 := by
    intro a j h
    simp [idFrame, h]
  have eF := lhwline_diag hn ν F hcolF (idFrame K r n) hD
  have eH := lhwline_diag hn ν (hw K hn ν) hcolH (idFrame K r n) hD
  have hev1 := eval_idFrame_hw K hn ν
  have hDmem : lhwline_mnu hn ν ∈ (hw K hn ν).support := by
    rw [mem_support_iff]
    intro h0
    rw [h0, zero_mul, hev1] at eH
    exact one_ne_zero eH
  have hcoef : AddMonoidAlgebra.coeff F (lhwline_mnu hn ν) = c * AddMonoidAlgebra.coeff (hw K hn ν) (lhwline_mnu hn ν) := by
    have e : AddMonoidAlgebra.coeff F (lhwline_mnu hn ν) = AddMonoidAlgebra.coeff G (lhwline_mnu hn ν) := by
      rw [hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hDmem))]
    rw [e, hc, MvPolynomial.coeff_smul, smul_eq_mul]
  have hevF : eval (idFrame K r n) F = c := by
    rw [eF, hcoef, mul_assoc, ← eH, hev1, mul_one]
  rw [h1, h2, hevF]

end Formalism.L2.G.Model.TS
end
end

section

open MvPolynomial

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem lowerTri_of_interlaced {r n : ℕ} {m : Fin r × Fin n →₀ ℕ} (h : Interlaced m) : LowerTri m := by
  suffices key : ∀ (k : ℕ) (s : Fin n), s.val = k → ∀ a : Fin r, a.val < s.val → m (a, s) = 0 from
    fun a s has => key s.val s rfl a has
  intro k
  induction k with
  | zero =>
    intro s hs a ha
    omega
  | succ k ih =>
    intro s hs a ha
    have hk : k < n := by have := s.isLt; omega
    have h1 := h ⟨k, hk⟩ s (by simpa using hs) a
    have h2 : (∑ b : Fin r with b < a, m (b, (⟨k, hk⟩ : Fin n))) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hba : b < a := (Finset.mem_filter.mp hb).2
      have hba' : b.val < a.val := hba
      exact ih ⟨k, hk⟩ rfl b (by show b.val < k; omega)
    rw [h2, zero_add] at h1
    have h3 : m (a, s) ≤ ∑ b : Fin r with b ≤ a, m (b, s) :=
      Finset.single_le_sum (f := fun b => m (b, s)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ a, le_rfl⟩)
    omega

theorem lower_triangular_over_field : LowerTriK := by
  intro O K _ _ _ _ _ r n ν Q hQ
  have hlead : ∀ f ∈ dualWeyl K r n ν, f ≠ 0 → LowerTri ((colLex r n).degree f) := fun f hf hf0 =>
    lowerTri_of_interlaced (leadInterlaced K r n ν f hf hf0)
  refine ⟨?_, ?_⟩
  · suffices key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl K r n ν,
        (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → AddMonoidAlgebra.coeff f e ∈ Set.range (algebraMap O K)) →
        (colLex r n).toSyn ((colLex r n).degree f) = d → f ∈ (dualWeyl O r n ν).map (toK O K) by
      intro h
      exact key _ Q hQ h rfl
    intro d
    induction d using WellFoundedLT.induction with
    | _ d ih =>
      intro f hf hco hd
      by_cases hf0 : f = 0
      · rw [hf0]; exact Submodule.zero_mem _
      set m := (colLex r n).degree f with hm
      have hint : Interlaced m := leadInterlaced K r n ν f hf hf0
      have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t :=
        colSums K r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)
      obtain ⟨N, sz, hsz, I, hshape, hmono, hexp⟩ := sSYTExists r n ν m hcol hint
      obtain ⟨hbdeg, hblc⟩ := column_lex_bideterminant K r n N sz hsz I hmono
      have hbO : bideterminant O sz hsz I ∈ dualWeyl O r n ν := by
        have := bidetMem O r n N sz hsz I
        rw [hshape] at this
        exact this
      have hbK : bideterminant K sz hsz I ∈ dualWeyl K r n ν := by
        have := bidetMem K r n N sz hsz I
        rw [hshape] at this
        exact this
      have hmap : toK O K (bideterminant O sz hsz I) = bideterminant K sz hsz I :=
        ldlat_map_bidet (algebraMap O K) sz hsz I
      obtain ⟨c, hc⟩ := hco m (lowerTri_of_interlaced hint)
      have hc' : (colLex r n).leadingCoeff f = algebraMap O K c := hc.symm
      have hcb : (colLex r n).leadingCoeff f • bideterminant K sz hsz I = toK O K (c • bideterminant O sz hsz I) := by
        rw [map_smul, hmap, hc', algebraMap_smul]
      have hcbmem : (colLex r n).leadingCoeff f • bideterminant K sz hsz I ∈ (dualWeyl O r n ν).map (toK O K) := by
        rw [hcb]
        exact Submodule.mem_map_of_mem (Submodule.smul_mem _ _ hbO)
      set f' := f - (colLex r n).leadingCoeff f • bideterminant K sz hsz I with hf'
      have hf'mem : f' ∈ dualWeyl K r n ν :=
        Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hbK)
      have hdecomp : f = f' + (colLex r n).leadingCoeff f • bideterminant K sz hsz I := by
        rw [hf']; abel
      rw [hdecomp]
      refine Submodule.add_mem _ ?_ hcbmem
      by_cases h0 : f' = 0
      · rw [h0]; exact Submodule.zero_mem _
      have hlt := lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant K sz hsz I) (hbdeg.trans hexp) hblc h0
      refine ih _ (hd ▸ hlt) f' hf'mem ?_ rfl
      intro e he
      obtain ⟨x, hx⟩ := hco e he
      refine ⟨x - AddMonoidAlgebra.coeff (c • bideterminant O sz hsz I) e, ?_⟩
      have hce : AddMonoidAlgebra.coeff (toK O K (c • bideterminant O sz hsz I)) e = algebraMap O K (AddMonoidAlgebra.coeff (c • bideterminant O sz hsz I) e) :=
        coeff_map (algebraMap O K) _ e
      rw [hf', MvPolynomial.coeff_sub, hcb, map_sub, hx, hce]
  · intro h
    by_contra hQ0
    exact ((colLex r n).coeff_degree_ne_zero_iff).mpr hQ0 (h _ (hlead Q hQ hQ0))

end Formalism.L2.G.Model.TS
end

section

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

lemma adj_fockR_of_subset {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) (s : Finset (σ →₀ ℕ))
    (h : f.support ⊆ s) :
    fockR f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  unfold fockR
  apply Finset.sum_subset h
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm]
  ring

lemma adj_fockR_add_left {σ R : Type*} [CommRing R] (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := by
  classical
  rw [adj_fockR_of_subset _ _ (f.support ∪ f'.support) MvPolynomial.support_add,
    adj_fockR_of_subset f g (f.support ∪ f'.support) Finset.subset_union_left,
    adj_fockR_of_subset f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.coeff_add]
  ring

lemma adj_fockR_smul_left {σ R : Type*} [CommRing R] (a : R) (f g : MvPolynomial σ R) :
    fockR (a • f) g = a * fockR f g := by
  rw [adj_fockR_of_subset _ _ f.support MvPolynomial.support_smul, fockR, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

lemma adj_fockR_symm {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) :
    fockR f g = fockR g f := by
  classical
  rw [adj_fockR_of_subset f g (f.support ∪ g.support) Finset.subset_union_left,
    adj_fockR_of_subset g f (f.support ∪ g.support) Finset.subset_union_right]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma adj_fockR_add_right {σ R : Type*} [CommRing R] (f g g' : MvPolynomial σ R) :
    fockR f (g + g') = fockR f g + fockR f g' := by
  rw [adj_fockR_symm, adj_fockR_add_left, adj_fockR_symm g, adj_fockR_symm g']

lemma adj_fockR_smul_right {σ R : Type*} [CommRing R] (a : R) (f g : MvPolynomial σ R) :
    fockR f (a • g) = a * fockR f g := by
  rw [adj_fockR_symm, adj_fockR_smul_left, adj_fockR_symm]

lemma adj_fockR_map {σ R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f g : MvPolynomial σ R) :
    fockR (map φ f) (map φ g) = φ (fockR f g) := by

  rw [adj_fockR_of_subset _ _ f.support (MvPolynomial.support_map_subset _ _), fockR, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp [MvPolynomial.coeff_map]

lemma adj_fockR_rat {σ : Type*} (f g : MvPolynomial σ ℚ) : fockR f g = fockQ f g := rfl

lemma adj_rowDiv_int {r n : ℕ} (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) ℤ) :
    fockR (rowDiv ℤ a b k f) g = fockR f (rowDiv ℤ b a k g) := by
  apply Int.cast_injective (α := ℚ)
  have e1 := adj_fockR_map (Int.castRingHom ℚ) (rowDiv ℤ a b k f) g
  have e2 := adj_fockR_map (Int.castRingHom ℚ) f (rowDiv ℤ b a k g)
  simp only [eq_intCast] at e1 e2
  rw [← e1, ← e2, ← lclosedeq_rowDiv_map, ← lclosedeq_rowDiv_map, adj_fockR_rat, adj_fockR_rat]
  exact fockQRowDivAdj r n a b k _ _

lemma adj_monomial_eq {σ R : Type*} [CommRing R] (m : σ →₀ ℕ) (c : R) :
    (monomial m c : MvPolynomial σ R) = c • map (Int.castRingHom R) (monomial m (1 : ℤ)) := by
  rw [MvPolynomial.map_monomial, map_one, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem fock_pairing_divided_adjoint : FockRRowDivAdj := by
  intro R _ r n a b k f g
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    induction g using MvPolynomial.induction_on' with
    | monomial m' c' =>
      rw [adj_monomial_eq m c, adj_monomial_eq m' c', rowDiv_smul, rowDiv_smul,
        lclosedeq_rowDiv_map, lclosedeq_rowDiv_map]
      rw [adj_fockR_smul_left, adj_fockR_smul_right, adj_fockR_smul_left, adj_fockR_smul_right,
        adj_fockR_map, adj_fockR_map, adj_rowDiv_int]
    | add g1 g2 h1 h2 =>
      rw [rowDiv_add, adj_fockR_add_right, adj_fockR_add_right, h1, h2]
  | add f1 f2 h1 h2 =>
    rw [rowDiv_add, adj_fockR_add_left, adj_fockR_add_left, h1, h2]

lemma adj_applyWord_cons {R : Type*} [CommRing R] {r n : ℕ} (x : Fin r × Fin r × ℕ)
    (w : List (Fin r × Fin r × ℕ)) (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (x :: w) F = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w F) := by
  rfl

lemma adj_applyWord_append {R : Type*} [CommRing R] {r n : ℕ} (l1 l2 : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (l1 ++ l2) F = applyWord R l1 (applyWord R l2 F) := by
  unfold applyWord
  rw [List.foldr_append]

lemma adj_transposeWord_cons {r : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (x :: w) = transposeWord w ++ [(x.2.1, x.1, x.2.2)] := by
  simp [transposeWord]

theorem fock_pairing_word_adjoint : FockRWordAdj := by
  intro R _ r n w
  induction w with
  | nil =>
    intro F G
    rfl
  | cons x w ih =>
    intro F G
    rw [adj_applyWord_cons, fock_pairing_divided_adjoint R r n x.1 x.2.1 x.2.2, ih, adj_transposeWord_cons,
      adj_applyWord_append]
    rfl

end Formalism.L2.G.Model.TS
end
end
