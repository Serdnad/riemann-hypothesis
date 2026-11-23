module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle006
public import Mathlib.CategoryTheory.Category.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ColumnAntisymmetry

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem split {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (col : Fin m → ℕ) (hmono : Monotone col)
    (hc : ∀ i j : Fin m, Commute (xJ E i) (xJ E j))
    (hP : ∀ i j : Fin m, (i : ℕ) + 1 = j →
      xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 ∧
      ∀ k : Fin m, k ≠ i → k ≠ j → Commute (xJ E k) (pm (Equiv.swap i j)))
    (i j : Fin m) (hij : (i : ℕ) + 1 = j) (hcol : col i = col j) :
    ∃ R : Module.End ℂ (TV n M (Fin m)), colD E col = (xJ E i - xJ E j + 1) * R ∧
      R * pm (Equiv.swap i j) = pm (Equiv.swap i j) * R := by
  set s : Module.End ℂ (TV n M (Fin m)) := pm (Equiv.swap i j) with hs_def
  have hs2 : s * s = 1 := by rw [hs_def, ← pm_mul, Equiv.swap_mul_self, pm_one]
  obtain ⟨h1, h2⟩ := hP i j hij
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have hlt : i < j := by
    rw [Fin.lt_iff_val_lt_val]
    omega
  have h3 : s * xJ E j = xJ E i * s + 1 := by
    calc s * xJ E j = s * (xJ E j * s) * s := by simp only [mul_assoc, hs2, mul_one]
      _ = s * (s * xJ E i + 1) * s := by rw [h1]
      _ = xJ E i * s + 1 := by
        rw [mul_add, add_mul, ← mul_assoc s s, hs2, one_mul, mul_one, hs2]
  have e1 : Commute (xJ E i + xJ E j) s := by
    show (xJ E i + xJ E j) * s = s * (xJ E i + xJ E j)
    rw [add_mul, mul_add, h1, h3]
    abel
  have e2 : Commute (xJ E i * xJ E j) s := by
    show xJ E i * xJ E j * s = s * (xJ E i * xJ E j)
    rw [mul_assoc, h1, (hc i j).eq, ← mul_assoc, h3]
    noncomm_ring
  have hsym : ∀ c, Commute c s → Commute c (xJ E i) →
      Commute ((xJ E i + c) * (xJ E j + c)) s := by
    intro c hcs hci
    have hexp : (xJ E i + c) * (xJ E j + c) =
        xJ E i * xJ E j + c * (xJ E i + xJ E j) + c * c := by
      rw [add_mul, mul_add, mul_add, mul_add, ← hci.eq]
      abel
    rw [hexp]
    exact (e2.add_left (hcs.mul_left e1)).add_left (hcs.mul_left hcs)
  have hsym2 : ∀ c, Commute c s → Commute c (xJ E i) →
      Commute ((c - xJ E i) * (c - xJ E j)) s := by
    intro c hcs hci
    have hh := hsym (-c) hcs.neg_left hci.neg_left
    rwa [show (c - xJ E i) * (c - xJ E j) = (xJ E i + -c) * (xJ E j + -c) by noncomm_ring]
  let S : Set (Module.End ℂ (TV n M (Fin m))) := Set.range (xJ E)
  have hcomm : S.Pairwise Commute := by
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ _
    exact hc k l
  let _ : IsMulCommutative (Algebra.adjoin ℂ S) := Algebra.isMulCommutative_adjoin ℂ hcomm
  let _ : CommRing (Algebra.adjoin ℂ S) :=
    open scoped IsMulCommutative in inferInstance
  let x' : Fin m → Algebra.adjoin ℂ S := fun k => ⟨xJ E k, Algebra.subset_adjoin ⟨k, rfl⟩⟩
  let F : Fin m → Fin m → Algebra.adjoin ℂ S := fun p q =>
    if p < q ∧ col p = col q then x' p - x' q + 1 else 1
  have hF : ∀ p q, ((F p q : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) =
      if p < q ∧ col p = col q then xJ E p - xJ E q + 1 else 1 := by
    intro p q
    simp only [F]
    split_ifs <;> rfl
  have hcoe_mul : ∀ a b : Algebra.adjoin ℂ S,
      ((a * b : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) = a * b := fun a b => rfl
  have hcoe_one : ((1 : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) = 1 := rfl
  have hlist : ∀ l : List (Algebra.adjoin ℂ S),
      ((l.prod : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) =
        (l.map Subtype.val).prod := by
    intro l
    induction l with
    | nil => exact hcoe_one
    | cons a l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, hcoe_mul, ih]
  have hcolD : colD E col = ((∏ q, ∏ p, F p q : Algebra.adjoin ℂ S) : Module.End ℂ _) := by
    simp only [colD, ← List.prod_ofFn, hlist, List.map_ofFn, Function.comp_def, hF]
  have hjmem : j ∈ (Finset.univ : Finset (Fin m)).erase i :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  have hsplit : ∀ g : Fin m → Algebra.adjoin ℂ S,
      ∏ q, g q = g i * g j * ∏ q ∈ (Finset.univ.erase i).erase j, g q := by
    intro g
    rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ g hjmem, mul_assoc]
  have hmemO : ∀ p, p ∈ (Finset.univ.erase i).erase j → p ≠ i ∧ p ≠ j := by
    intro p hp
    simp only [Finset.mem_erase] at hp
    exact ⟨hp.2.1, hp.1⟩
  have Fii : F i i = 1 := by simp [F]
  have Fjj : F j j = 1 := by simp [F]
  have Fji : F j i = 1 := by
    simp only [F]
    rw [if_neg]
    rintro ⟨h, -⟩
    exact absurd (lt_trans h hlt) (lt_irrefl _)
  have hPeq : ∏ q, ∏ p, F p q = F i j *
      ((∏ p ∈ (Finset.univ.erase i).erase j, F p i * F p j) *
        (∏ q ∈ (Finset.univ.erase i).erase j, F i q * F j q) *
        ∏ q ∈ (Finset.univ.erase i).erase j, ∏ p ∈ (Finset.univ.erase i).erase j, F p q) := by
    simp only [hsplit, Fii, Fjj, Fji, one_mul, mul_one, Finset.prod_mul_distrib]
    ring
  refine ⟨(((∏ p ∈ (Finset.univ.erase i).erase j, F p i * F p j) *
        (∏ q ∈ (Finset.univ.erase i).erase j, F i q * F j q) *
        ∏ q ∈ (Finset.univ.erase i).erase j, ∏ p ∈ (Finset.univ.erase i).erase j, F p q :
          Algebra.adjoin ℂ S) : Module.End ℂ _), ?_, ?_⟩
  · rw [hcolD, hPeq, hcoe_mul, hF, if_pos ⟨hlt, hcol⟩]
  · have hmul : ∀ a b : Algebra.adjoin ℂ S,
        Commute (a : Module.End ℂ (TV n M (Fin m))) s →
        Commute (b : Module.End ℂ (TV n M (Fin m))) s →
        Commute ((a * b : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) s := by
      intro a b ha hb
      rw [hcoe_mul]
      exact ha.mul_left hb
    have hone : Commute ((1 : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) s := by
      rw [hcoe_one]
      exact Commute.one_left s
    have hA : Commute (((∏ p ∈ (Finset.univ.erase i).erase j, F p i * F p j :
        Algebra.adjoin ℂ S)) : Module.End ℂ (TV n M (Fin m))) s := by
      refine Finset.prod_induction _ (fun b : Algebra.adjoin ℂ S =>
        Commute (b : Module.End ℂ (TV n M (Fin m))) s) hmul hone ?_
      intro p hp
      obtain ⟨hpi, hpj⟩ := hmemO p hp
      have hpi' : (p : ℕ) ≠ i := fun h => hpi (Fin.ext h)
      show Commute ((F p i : Module.End ℂ (TV n M (Fin m))) * (F p j : Module.End ℂ _)) s
      rw [hF, hF]
      by_cases hq : p < i ∧ col p = col i
      · rw [if_pos hq, if_pos ⟨lt_trans hq.1 hlt, hq.2.trans hcol⟩,
          show xJ E p - xJ E i + 1 = (xJ E p + 1) - xJ E i by abel,
          show xJ E p - xJ E j + 1 = (xJ E p + 1) - xJ E j by abel]
        exact hsym2 _ ((h2 p hpi hpj).add_left (Commute.one_left s))
          ((hc p i).add_left (Commute.one_left _))
      · have hn : ¬ (p < j ∧ col p = col j) := by
          rintro ⟨h, h'⟩
          apply hq
          refine ⟨?_, h'.trans hcol.symm⟩
          rw [Fin.lt_iff_val_lt_val] at h ⊢
          omega
        rw [if_neg hq, if_neg hn, mul_one]
        exact Commute.one_left s
    have hB : Commute (((∏ q ∈ (Finset.univ.erase i).erase j, F i q * F j q :
        Algebra.adjoin ℂ S)) : Module.End ℂ (TV n M (Fin m))) s := by
      refine Finset.prod_induction _ (fun b : Algebra.adjoin ℂ S =>
        Commute (b : Module.End ℂ (TV n M (Fin m))) s) hmul hone ?_
      intro q hq
      obtain ⟨hqi, hqj⟩ := hmemO q hq
      have hqj' : (q : ℕ) ≠ j := fun h => hqj (Fin.ext h)
      show Commute ((F i q : Module.End ℂ (TV n M (Fin m))) * (F j q : Module.End ℂ _)) s
      rw [hF, hF]
      by_cases hq' : i < q ∧ col i = col q
      · have hjq : j < q := by
          have := hq'.1
          rw [Fin.lt_iff_val_lt_val] at this ⊢
          omega
        rw [if_pos hq', if_pos ⟨hjq, hcol.symm.trans hq'.2⟩,
          show xJ E i - xJ E q + 1 = xJ E i + (1 - xJ E q) by abel,
          show xJ E j - xJ E q + 1 = xJ E j + (1 - xJ E q) by abel]
        exact hsym _ ((Commute.one_left s).sub_left (h2 q hqi hqj))
          ((Commute.one_left _).sub_left (hc q i))
      · have hn : ¬ (j < q ∧ col j = col q) := by
          rintro ⟨h, h'⟩
          apply hq'
          refine ⟨?_, hcol.trans h'⟩
          rw [Fin.lt_iff_val_lt_val] at h ⊢
          omega
        rw [if_neg hq', if_neg hn, mul_one]
        exact Commute.one_left s
    have hC : Commute (((∏ q ∈ (Finset.univ.erase i).erase j,
        ∏ p ∈ (Finset.univ.erase i).erase j, F p q :
        Algebra.adjoin ℂ S)) : Module.End ℂ (TV n M (Fin m))) s := by
      refine Finset.prod_induction _ (fun b : Algebra.adjoin ℂ S =>
        Commute (b : Module.End ℂ (TV n M (Fin m))) s) hmul hone ?_
      intro q hq
      refine Finset.prod_induction _ (fun b : Algebra.adjoin ℂ S =>
        Commute (b : Module.End ℂ (TV n M (Fin m))) s) hmul hone ?_
      intro p hp
      obtain ⟨hqi, hqj⟩ := hmemO q hq
      obtain ⟨hpi, hpj⟩ := hmemO p hp
      show Commute (F p q : Module.End ℂ (TV n M (Fin m))) s
      rw [hF]
      split_ifs
      · exact ((h2 p hpi hpj).sub_left (h2 q hqi hqj)).add_left (Commute.one_left s)
      · exact Commute.one_left s
    exact (hmul _ _ (hmul _ _ hA hB) hC).eq

end ColumnAntisymmetry

end PositivityTheory.Rg.Cz

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace CurryingSwaps

variable {α : Type*} {m k : ℕ}

theorem upd_castAdd (I : Fin m → α) (J : Fin k → α) (i : Fin m) (v : α) :
    Function.update (Fin.append I J) (Fin.castAdd k i) v = Fin.append (Function.update I i v) J := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) x
  · by_cases h : i' = i
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.castAdd_injective _ _ e)), Fin.append_left, Fin.append_left,
        Function.update_of_ne h]
  · rw [Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega), Fin.append_right, Fin.append_right]

theorem upd_natAdd (I : Fin m → α) (J : Fin k → α) (j : Fin k) (v : α) :
    Function.update (Fin.append I J) (Fin.natAdd m j) v = Fin.append I (Function.update J j v) := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) x
  · rw [Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega), Fin.append_left, Fin.append_left]
  · by_cases h : j' = j
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.natAdd_injective _ _ e)), Fin.append_right, Fin.append_right,
        Function.update_of_ne h]

theorem swap_castAdd (I : Fin m → α) (J : Fin k → α) (i i' : Fin m) :
    Fin.append I J ∘ Equiv.swap (Fin.castAdd k i) (Fin.castAdd k i') = Fin.append (I ∘ Equiv.swap i i') J := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · simp only [Function.comp_apply, Fin.append_left, Equiv.swap_apply_def, Fin.castAdd_inj]
    split_ifs <;> simp
  · have h1 : Fin.natAdd m b ≠ Fin.castAdd k i := fun e => by simp [Fin.ext_iff] at e; omega
    have h2 : Fin.natAdd m b ≠ Fin.castAdd k i' := fun e => by simp [Fin.ext_iff] at e; omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right]

theorem swap_natAdd (I : Fin m → α) (J : Fin k → α) (j j' : Fin k) :
    Fin.append I J ∘ Equiv.swap (Fin.natAdd m j) (Fin.natAdd m j') = Fin.append I (J ∘ Equiv.swap j j') := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · have h1 : Fin.castAdd k a ≠ Fin.natAdd m j := fun e => by simp [Fin.ext_iff] at e; omega
    have h2 : Fin.castAdd k a ≠ Fin.natAdd m j' := fun e => by simp [Fin.ext_iff] at e; omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left]
  · simp only [Function.comp_apply, Fin.append_right, Equiv.swap_apply_def, Fin.natAdd_inj]
    split_ifs <;> simp

theorem swap_mixed (I : Fin m → α) (J : Fin k → α) (i : Fin m) (j : Fin k) :
    Fin.append I J ∘ Equiv.swap (Fin.castAdd k i) (Fin.natAdd m j) =
      Fin.append (Function.update I i (J j)) (Function.update J j (I i)) := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · have h2 : Fin.castAdd k a ≠ Fin.natAdd m j := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases h : a = i
    · subst h; simp
    · have h1 : Fin.castAdd k a ≠ Fin.castAdd k i := fun e => h (Fin.castAdd_injective _ _ e)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left,
        Function.update_of_ne h]
  · have h1 : Fin.natAdd m b ≠ Fin.castAdd k i := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases h : b = j
    · subst h; simp
    · have h2 : Fin.natAdd m b ≠ Fin.natAdd m j := fun e => h (Fin.natAdd_injective _ _ e)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right,
        Function.update_of_ne h]

theorem iteApp {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (p : Prop) [Decidable p]
    (g : V →ₗ[ℂ] W) (x : V) : (if p then g else 0) x = if p then g x else 0 := by
  split_ifs <;> rfl

end CurryingSwaps

open CurryingSwaps in
theorem curry_holds : Curry := by
  intro n M _ _ E m k
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g h
    funext K
    have := congrFun (congrFun (congrArg (fun x => x) h) (fun j => K (Fin.natAdd m j))) (fun i => K (Fin.castAdd k i))
    simpa only [curF_apply, Fin.append_castAdd_natAdd] using this
  · intro g
    refine ⟨fun K => g (fun j => K (Fin.natAdd m j)) (fun i => K (Fin.castAdd k i)), ?_⟩
    funext J I
    simp only [curF_apply, Fin.append_left, Fin.append_right]
  · intro a b
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, tE_apply, Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right, upd_castAdd, upd_natAdd, add_assoc]
  · intro i
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    have hz : ∀ b : Fin k, ¬ (Fin.natAdd m b < Fin.castAdd k i) := fun b h => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] at h <;> omega
    have hc : ∀ x : Fin m, Fin.castAdd k x < Fin.castAdd k i ↔ x < i := fun x => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    simp only [xJ, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, Om_apply, LinearMap.sum_apply,
      Finset.sum_apply, pm_apply, iteApp, ite_apply, Pi.zero_apply, lift_apply, curF_apply, Fin.append_left, upd_castAdd, Finset.sum_filter,
      Fin.sum_univ_add, swap_castAdd, hz, hc, if_false, Finset.sum_const_zero, add_zero]
  · intro j
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    have hz : ∀ x : Fin m, Fin.castAdd k x < Fin.natAdd m j := fun x => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    have hc : ∀ b : Fin k, Fin.natAdd m b < Fin.natAdd m j ↔ b < j := fun b => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    simp only [xJ, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, Om_apply, LinearMap.sum_apply,
      Finset.sum_apply, pm_apply, iteApp, ite_apply, Pi.zero_apply, curF_apply, tE_apply, Fin.append_right, upd_natAdd, upd_castAdd,
      Finset.sum_filter, Fin.sum_univ_add, swap_natAdd, swap_mixed, hz, hc, if_true, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun x p => if I p = x then
      f (Fin.append (Function.update I p (J j)) (Function.update J j x)) else 0)]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, add_assoc]
  · intro B
    rfl
  · intro i i'
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, pm_apply, lift_apply, swap_castAdd]
  · intro j j'
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, pm_apply, swap_natAdd]

end PositivityTheory.Rg.Cz

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem qdet_map' {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin m → Fin m → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  simp [qdet, qminor, Tm, map_list_prod, List.map_ofFn, Function.comp_def, apply_ite φ]

theorem qdet_commute {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (u : ℂ) (Z : A)
    (h : ∀ a b, Commute (E a b) Z) : Commute (qdet E u) Z := by
  unfold qdet qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  refine Commute.mul_left (Int.cast_commute _ _) (Commute.list_prod_left _ _ ?_)
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Commute.add_left ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_left _ _
  · exact Commute.zero_left _

theorem glRel_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin m → Fin m → A) (h : GlRel E) : GlRel fun a b => φ (E a b) := by
  intro a b c d
  dsimp only
  rw [← map_mul, ← map_mul, ← map_sub, h a b c d]
  split_ifs <;> simp

theorem comm_of_mem_adjoin {A : Type*} [Ring A] [Algebra ℂ A] {s : Set A} {X Z : A}
    (hX : X ∈ Algebra.adjoin ℂ s) (h : ∀ T ∈ s, Commute T Z) : Commute X Z := by
  have hs : s ⊆ Subalgebra.centralizer ℂ {Z} := fun T hT => by
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (h T hT).symm.eq
  have hX' := Algebra.adjoin_le hs hX
  rw [Subalgebra.mem_centralizer_iff] at hX'
  exact (hX' Z rfl).symm

variable {P : Type} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
@[simp] theorem liftA_apply (B : Module.End ℂ M) : liftA n M P B = lift B := rfl

omit [Fintype P] [DecidableEq P] in
theorem qdet_lift (F : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℂ) (h : HasChar F l) :
    HasChar (fun a b => (lift (F a b) : Module.End ℂ (TV n M P))) l := by
  intro u
  have e : (fun a b => (lift (F a b) : Module.End ℂ (TV n M P))) = fun a b => liftA n M P (F a b) := by
    funext a b
    rw [liftA_apply]
  rw [e, ← qdet_map', h u, AlgHom.commutes]

omit [Fintype P] in
theorem tE_empty (F : Fin n → Fin n → Module.End ℂ M) :
    (tE (∅ : Finset P) F : Fin n → Fin n → Module.End ℂ (TV n M P)) = fun a b => lift (F a b) := by
  funext a b
  simp [tE]

omit [Fintype P] in
theorem tE_comm_lift (S : Finset P) (F : Fin n → Fin n → Module.End ℂ M) (B : Module.End ℂ M)
    (h : ∀ c d, Commute (F c d) B) (a b : Fin n) :
    Commute (tE S F a b : Module.End ℂ (TV n M P)) (lift B) := by
  unfold tE
  refine Commute.add_left ?_ (Commute.sum_left _ _ _ fun p _ => ?_)
  · have hc := (h a b).map (liftA n M P)
    simpa only [liftA_apply] using hc
  · unfold Commute SemiconjBy
    refine LinearMap.ext fun x => funext fun I => ?_
    simp only [Module.End.mul_apply, eAt, lift, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    split_ifs <;> simp

theorem cA_lift {C : Type} [DecidableEq C] (col : P → C) (b : P → Fin n) (B : Module.End ℂ M) :
    cA col b ∘ₗ lift B = B ∘ₗ (cA col b : TV n M P →ₗ[ℂ] M) := by
  refine LinearMap.ext fun x => ?_

  simp [cA, alt, pm, lift, LinearMap.sum_apply, map_sum, map_zsmul]

def cj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    Module.End ℂ W →ₐ[ℂ] Module.End ℂ V where
  toFun X := e.symm.toLinearMap ∘ₗ X ∘ₗ e.toLinearMap
  map_one' := LinearMap.ext fun v => by simp
  map_mul' X Y := LinearMap.ext fun v => by simp
  map_zero' := LinearMap.ext fun v => by simp
  map_add' X Y := LinearMap.ext fun v => by simp
  commutes' r := LinearMap.ext fun v => by simp

theorem cj_apply {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (X : Module.End ℂ W) (v : V) : cj e X v = e.symm (X (e v)) := rfl

end PositivityTheory.Rg.Cz.TA

end
end
