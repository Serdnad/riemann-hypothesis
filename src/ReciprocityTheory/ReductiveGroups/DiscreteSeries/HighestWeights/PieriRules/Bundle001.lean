module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

def lowCompLin {n : ℕ} (μ : Fin n → ℝ) : ℝ :=
  ∑ c : Fin n, ((c : ℕ) : ℝ) * μ c

theorem lowComp_tensAct_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*}
    [Fintype ι] {n : ℕ} (A : Fin n → Fin n → Module.End ℂ V) (M : Fin n → Fin n → Matrix ι ι ℂ)
    (a b : Fin n) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensAct A M a b x i = A a b (x i) + ∑ j, M a b i j • x j := by
  simp [tensAct]

theorem lowComp_entry_wt {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ε : Fin n → Bool}
    {M : Fin n → Fin n → Matrix ι ι ℂ} {γ : ι → Fin n → ℝ}
    (hM : Formalism.REAL.KRel ε M) (hd : ∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ))
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) {j k : ι} (hne : M a b j k ≠ 0) (c : Fin n) :
    γ k c = γ j c + ((if c = b then 1 else 0) - (if c = a then 1 else 0)) := by
  have h := congrFun (congrFun (hM a b c c he rfl) j) k
  rw [hd c] at h
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hba : b ≠ a := ne_of_gt hab
  have key : ((γ k c : ℝ) : ℂ) - ((γ j c : ℝ) : ℂ) =
      (((if c = b then 1 else 0) - (if c = a then 1 else 0) : ℝ) : ℂ) := by
    by_cases hcb : c = b
    · subst hcb
      have hca : ¬ c = a := hba
      simp only [if_neg hca, ite_true, Matrix.zero_apply, sub_zero] at h
      simp only [if_neg hca]
      apply mul_left_cancel₀ hne
      push_cast
      linear_combination h
    · by_cases hca : c = a
      · subst hca
        simp only [if_neg (Ne.symm hcb), ite_true, Matrix.zero_apply, zero_sub] at h
        simp only [if_neg hcb]
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination h
      · simp only [if_neg (Ne.symm hcb), if_neg hca, Matrix.zero_apply, sub_zero] at h
        simp only [if_neg hcb, if_neg hca]
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination h
  have key' : ((γ k c - γ j c : ℝ) : ℂ) =
      (((if c = b then 1 else 0) - (if c = a then 1 else 0) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub (γ k c)]; exact key
  have := Complex.ofReal_injective key'
  linarith

theorem lowComp_lin_entry {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ε : Fin n → Bool}
    {M : Fin n → Fin n → Matrix ι ι ℂ} {γ : ι → Fin n → ℝ}
    (hM : Formalism.REAL.KRel ε M) (hd : ∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ))
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) {j k : ι} (hne : M a b j k ≠ 0) :
    lowCompLin (γ k) = lowCompLin (γ j) + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  have hk := lowComp_entry_wt hM hd hab he hne
  unfold lowCompLin
  simp only [hk, mul_add, mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem lowComp : LowCompStatement := by
  intro V _ _ n ε A ι _ _ M γ hM hd ν x hx hhw
  classical
  obtain ⟨hwt, hup⟩ := hhw
  set S : Finset ι := Finset.univ.filter (fun i => x i ≠ 0) with hS
  have hSne : S.Nonempty := by
    by_contra h
    apply hx
    ext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using hi⟩⟩
  obtain ⟨i0, hi0, hmax⟩ := S.exists_max_image (fun i => lowCompLin (γ i)) hSne
  refine ⟨γ i0, ⟨i0, rfl, (Finset.mem_filter.1 hi0).2⟩, ?_⟩
  intro j hj
  constructor
  · intro c
    have h := congrArg (fun y : PiLp 2 (fun _ : ι => V) => y j) (hwt c)
    simp only [lowComp_tensAct_apply, hd c, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, PiLp.smul_apply] at h
    rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h, hj]
    abel
  · intro a b hab he
    have h := congrArg (fun y : PiLp 2 (fun _ : ι => V) => y j) (hup a b hab he)
    simp only [lowComp_tensAct_apply, PiLp.zero_apply] at h
    have hsum : ∑ k, M a b j k • x k = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hne : M a b j k = 0
      · simp [hne]
      · have hxk : x k = 0 := by
          by_contra hxk
          have hle := hmax k (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxk⟩)
          have hl := lowComp_lin_entry hM hd hab he hne
          rw [hj] at hl
          have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
          linarith
        simp [hxk]
    rw [hsum, add_zero] at h
    exact h

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem pieriSt_kRel_stdM {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.KRel ε (stdM n) := by
  intro a b c d _ _
  simp only [stdM]
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1 h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
  · simp [Matrix.single_mul_single_of_ne, h1, h2]

theorem pieriSt_stdM_diag {n : ℕ} (a : Fin n) :
    stdM n a a = Matrix.diagonal fun i => ((stdWt n i a : ℝ) : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hai : a = i
    · subst hai; simp [stdM, stdWt]
    · simp [stdM, stdWt, hai, Pi.single_apply]
  · simp [stdM, Matrix.single_apply, hij]
    intro h1 h2; exact hij (h1.symm.trans h2)

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem weylRatio_rhoC_sub_ge_one {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b)
    (he : ε a = ε b) : 1 ≤ rhoC ε a - rhoC ε b := by
  have h1 : (univ.filter fun x => b < x ∧ ε x = ε b).card + 1 ≤
      (univ.filter fun x => a < x ∧ ε x = ε a).card := by
    apply Nat.succ_le_of_lt
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨b, by simp [hab, he], by simp⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hab.trans hx.1, hx.2.trans he.symm⟩
  have h2 : (univ.filter fun x => x < a ∧ ε x = ε a).card + 1 ≤
      (univ.filter fun x => x < b ∧ ε x = ε b).card := by
    apply Nat.succ_le_of_lt
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨a, by simp [hab, he], by simp⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hx.1.trans hab, hx.2.trans he⟩
  have h1' : ((univ.filter fun x => b < x ∧ ε x = ε b).card : ℝ) + 1 ≤
      ((univ.filter fun x => a < x ∧ ε x = ε a).card : ℝ) := by exact_mod_cast h1
  have h2' : ((univ.filter fun x => x < a ∧ ε x = ε a).card : ℝ) + 1 ≤
      ((univ.filter fun x => x < b ∧ ε x = ε b).card : ℝ) := by exact_mod_cast h2
  simp only [rhoC]
  linarith

theorem weylRatio_prodW {n : ℕ} (ε : Fin n → Bool) (s : Fin n) (h : Fin n → ℝ) :
    ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ ε a = ε b),
        (if b = s then h a else if a = s then h b else 1) =
      ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), h b := by
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ s)]
  have h1 : ∏ b ∈ univ.filter (fun b => s < b ∧ ε s = ε b),
      (if b = s then h s else if s = s then h b else 1) =
        ∏ b ∈ univ.filter (fun b => s < b ∧ ε s = ε b), h b :=
    Finset.prod_congr rfl fun b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp [ne_of_gt hb.1]
  have h2 : ∏ a ∈ univ.erase s, ∏ b ∈ univ.filter (fun b => a < b ∧ ε a = ε b),
      (if b = s then h a else if a = s then h b else 1) =
        ∏ a ∈ univ.filter (fun a => a < s ∧ ε a = ε s), h a := by
    rw [Finset.prod_filter,
      ← Finset.mul_prod_erase univ (fun a => if a < s ∧ ε a = ε s then h a else 1) (Finset.mem_univ s)]
    simp only [lt_self_iff_false, false_and, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun a ha => ?_
    have has : a ≠ s := Finset.ne_of_mem_erase ha
    simp only [has, ↓reduceIte]
    rw [Finset.prod_ite_eq']
    simp [Finset.mem_filter]
  rw [h1, h2, ← Finset.prod_union]
  · congr 1
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨ne_of_gt h1, h2.symm⟩
      · exact ⟨ne_of_lt h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases lt_or_gt_of_ne h1 with h | h
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl ⟨h, h2.symm⟩
  · exact Finset.disjoint_filter.mpr fun b _ h1 h2 => lt_asymm h1.1 h2.1

theorem weylK_shift_mul {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (s : Fin n) (c : ℝ) :
    weylK ε (Λ + Pi.single s c) *
        ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), ((Λ + rhoC ε) s - (Λ + rhoC ε) b) =
      weylK ε Λ *
        ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), ((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) := by
  rw [← weylRatio_prodW ε s (fun b => (Λ + rhoC ε) s - (Λ + rhoC ε) b),
    ← weylRatio_prodW ε s (fun b => (Λ + rhoC ε) s - (Λ + rhoC ε) b + c)]
  simp only [weylK]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have hab : a ≠ b := ne_of_lt hb.1
  by_cases hbs : b = s
  · subst hbs
    simp only [Pi.add_apply, Pi.single_apply, hab, ↓reduceIte]
    ring
  · by_cases has : a = s
    · subst has
      simp only [Pi.add_apply, Pi.single_apply, hbs, ↓reduceIte]
      ring
    · simp only [Pi.add_apply, Pi.single_apply, hbs, has, ↓reduceIte]
      ring

theorem weylRatio_ell_ne {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) {s b : Fin n}
    (hbs : b ≠ s) (he : ε b = ε s) : (Λ + rhoC ε) s - (Λ + rhoC ε) b ≠ 0 := by
  intro h
  simp only [Pi.add_apply] at h
  rcases lt_or_gt_of_ne hbs with hlt | hlt
  · have h1 := weylRatio_rhoC_sub_ge_one ε hlt he
    have h2 := hΛ b s hlt he
    linarith
  · have h1 := weylRatio_rhoC_sub_ge_one ε hlt he.symm
    have h2 := hΛ s b hlt he.symm
    linarith

theorem weylRatio_prod_ne {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (s : Fin n) :
    ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), ((Λ + rhoC ε) s - (Λ + rhoC ε) b) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun b hb => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact weylRatio_ell_ne ε Λ hΛ hb.1 hb.2

theorem weylK_shift {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (s : Fin n) (c : ℝ) :
    weylK ε (Λ + Pi.single s c) =
      weylK ε Λ * ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
        (((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) / ((Λ + rhoC ε) s - (Λ + rhoC ε) b)) := by
  rw [Finset.prod_div_distrib, ← mul_div_assoc, eq_div_iff (weylRatio_prod_ne ε Λ hΛ s)]
  exact weylK_shift_mul ε Λ s c

theorem weylK_add_smul_single {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (s : Fin n)
    (c : ℝ) :
    weylK ε (Λ + c • (Pi.single s (1 : ℝ) : Fin n → ℝ)) = weylK ε Λ *
      ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
        ((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) / ((Λ + rhoC ε) s - (Λ + rhoC ε) b) := by
  have h : c • (Pi.single s (1 : ℝ) : Fin n → ℝ) = Pi.single s c := by
    ext x
    by_cases hx : x = s <;> simp [hx]
  rw [h]
  exact weylK_shift ε Λ hΛ s c

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS

private lemma weylPos_above_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    (univ.filter fun c => b < c ∧ ε c = ε b).card + 1 ≤ (univ.filter fun c => a < c ∧ ε c = ε a).card := by
  have hsub : (univ.filter fun c => b < c ∧ ε c = ε b) ⊆ (univ.filter fun c => a < c ∧ ε c = ε a) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨hab.trans hc.1, hc.2.trans he.symm⟩
  have hss : (univ.filter fun c => b < c ∧ ε c = ε b) ⊂ (univ.filter fun c => a < c ∧ ε c = ε a) := by
    rw [Finset.ssubset_iff_of_subset hsub]
    exact ⟨b, by simp [hab, he], by simp⟩
  exact Finset.card_lt_card hss

private lemma weylPos_below_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    (univ.filter fun c => c < a ∧ ε c = ε a).card + 1 ≤ (univ.filter fun c => c < b ∧ ε c = ε b).card := by
  have hsub : (univ.filter fun c => c < a ∧ ε c = ε a) ⊆ (univ.filter fun c => c < b ∧ ε c = ε b) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨hc.1.trans hab, hc.2.trans he⟩
  have hss : (univ.filter fun c => c < a ∧ ε c = ε a) ⊂ (univ.filter fun c => c < b ∧ ε c = ε b) := by
    rw [Finset.ssubset_iff_of_subset hsub]
    exact ⟨a, by simp [hab, he], by simp⟩
  exact Finset.card_lt_card hss

theorem rhoC_sub_ge_one {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    1 ≤ rhoC ε a - rhoC ε b := by
  have h1 := weylPos_above_lt ε hab he
  have h2 := weylPos_below_lt ε hab he
  have h1' : ((univ.filter fun c => b < c ∧ ε c = ε b).card : ℝ) + 1 ≤
      ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) := by exact_mod_cast h1
  have h2' : ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) + 1 ≤
      ((univ.filter fun c => c < b ∧ ε c = ε b).card : ℝ) := by exact_mod_cast h2
  unfold rhoC
  linarith

theorem rhoC_consec {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b)
    (hc : ∀ c, a < c → c < b → ε c ≠ ε a) : rhoC ε a - rhoC ε b = 1 := by
  have h1 := weylPos_above_lt ε hab he
  have h2 := weylPos_below_lt ε hab he
  have h3 : (univ.filter fun c => a < c ∧ ε c = ε a).card ≤
      (univ.filter fun c => b < c ∧ ε c = ε b).card + 1 := by
    refine (Finset.card_le_card ?_).trans (Finset.card_insert_le b _)
    intro c hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hc' ⊢
    rcases lt_trichotomy c b with h | h | h
    · exact absurd hc'.2 (hc c hc'.1 h)
    · exact Or.inl h
    · exact Or.inr ⟨h, hc'.2.trans he⟩
  have h4 : (univ.filter fun c => c < b ∧ ε c = ε b).card ≤
      (univ.filter fun c => c < a ∧ ε c = ε a).card + 1 := by
    refine (Finset.card_le_card ?_).trans (Finset.card_insert_le a _)
    intro c hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hc' ⊢
    rcases lt_trichotomy c a with h | h | h
    · exact Or.inr ⟨h, hc'.2.trans he.symm⟩
    · exact Or.inl h
    · exact absurd (hc'.2.trans he.symm) (hc c h hc'.1)
  have e1 : ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) =
      ((univ.filter fun c => b < c ∧ ε c = ε b).card : ℝ) + 1 := by
    exact_mod_cast le_antisymm h3 h1
  have e2 : ((univ.filter fun c => c < b ∧ ε c = ε b).card : ℝ) =
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) + 1 := by
    exact_mod_cast le_antisymm h4 h2
  unfold rhoC
  rw [e1, e2]
  ring

theorem weylPos : WeylPosStatement := by
  intro n ε μ hμ
  unfold weylK
  refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have hr := rhoC_sub_ge_one ε hb.1 hb.2
  have hd := hμ a b hb.1 hb.2
  apply div_pos
  · simp only [Pi.add_apply]
    linarith
  · linarith

end ReciprocityTheory.ChartRestriction.DS.HW
end
